import { createMuiTheme } from '@material-ui/core';
import Chip from '@material-ui/core/Chip';
import Icon from '@material-ui/core/Icon';
import Input from '@material-ui/core/Input';
import ListItem from '@material-ui/core/ListItem';
import MenuItem from '@material-ui/core/MenuItem';
import Modal from '@material-ui/core/Modal';
import Select from '@material-ui/core/Select';
import { withStyles } from '@material-ui/core/styles';
import Typography from '@material-ui/core/Typography';
import PropTypes from 'prop-types';
import React from 'react';
import { ThemeProvider } from 'styled-components';
import { CheckableItem } from './CheckableItem';
import {
    ColumnSelectionListStyled,
    ExportFieldSelectionContainerStyled,
    ExportOptionHeaderStyled,
    ExportOptionSelectStyled,
    IconButtonStyled,
    MainContainerStyled,
    MyPaper,
    RegionSelectionListStyled,
    SelectionListContainerStyled
} from './StyledExportModal';

const styles = theme => ({
    listItemOverride: {
        padding: '0'
    }
});

const theme = createMuiTheme({
    typography: {
        useNextVariants: true
    }
});

const ITEM_HEIGHT = 48;
const ITEM_PADDING_TOP = 8;
const MenuProps = {
    PaperProps: {
        style: {
            maxHeight: ITEM_HEIGHT * 4.5 + ITEM_PADDING_TOP,
            width: 250
        }
    }
};

class ExportModal extends React.Component {
    constructor(props) {
        super(props);
        this.exportOptions = [
            {
                label: 'CSV',
                value: 'csv'
            },
            {
                label: 'Excel',
                value: 'xls'
            }
        ];
        this.state = {
            modalIsOpen: this.props.modalProps.open,
            selectedExportOption: ['pdf'],
            selectedColumns: [],
            columnsDetail: [
                { columnName: 'Organization Name', isSelected: true },
                { columnName: 'Plan Code/Contract #', isSelected: false },
                { columnName: 'PBP', isSelected: false },
                { columnName: 'Segment', isSelected: true },
                { columnName: 'Plan Name', isSelected: true },
                { columnName: 'Product Type', isSelected: false },
                { columnName: 'Plan Type', isSelected: false },
                { columnName: 'Region', isSelected: true },
                { columnName: 'County', isSelected: false },
                { columnName: 'Current Enrollees', isSelected: false }
            ]
        };
        /* this.setState({
            modalIsOpen: this.props.modalProps.open
        }); */
    }

    componentWillReceiveProps(nextProps) {
        if (nextProps !== this.props) {
            console.log(nextProps);
            this.setState({
                modalIsOpen: nextProps.modalProps.open
            });
        }
    }

    closeModal = () => {
        this.setState({ modalIsOpen: false });
    };

    exportOptionOnChangeHandler = event => {
        this.setState({
            selectedExportOption: event.target.value
        });
    };

    selectAllHandler = event => {
        let columns = this.state.columnsDetail;
        columns = columns.map(column => {
            column.isSelected = true;
            return column;
        });

        this.setState({ columnsDetail: columns });
    };

    columnSelectionHandler = selectedColumn => () => {
        const currentIndex = this.state.columnsDetail.findIndex(
            column => column.columnName === selectedColumn.columnName
        );

        const columns = this.state.columnsDetail;

        columns[currentIndex].isSelected = !columns[currentIndex].isSelected;

        this.setState({ ...this.state, columnsDetail: columns });
    };

    render() {
        const { classes } = this.props;

        return (
            <div>
                <Modal
                    aria-labelledby="simple-modal-title"
                    aria-describedby="simple-modal-description"
                    open={this.state.modalIsOpen}
                    onClose={this.closeModal}
                >
                    <ThemeProvider theme={theme}>
                        <MyPaper>
                            <IconButtonStyled color="secondary">
                                <Icon>close</Icon>
                            </IconButtonStyled>

                            <MainContainerStyled elevation={1}>
                                <ExportOptionHeaderStyled>
                                    <Typography variant="subtitle2" gutterBottom>
                                        Export Option
                                    </Typography>

                                    <ExportOptionSelectStyled>
                                        {/* <InputLabel htmlFor="select-multiple">Export Option</InputLabel> */}
                                        <Select
                                            multiple
                                            onChange={this.exportOptionOnChangeHandler}
                                            renderValue={selected => (
                                                <div className={classes.chips}>
                                                    {selected.map(value => (
                                                        <Chip key={value} label={value} />
                                                    ))}
                                                </div>
                                            )}
                                            value={this.state.selectedExportOption}
                                            input={<Input id="select-multiple" />}
                                            MenuProps={MenuProps}
                                        >
                                            {this.exportOptions.map(option => (
                                                <MenuItem key={option.label} value={option.value}>
                                                    {option.label}
                                                </MenuItem>
                                            ))}
                                        </Select>
                                    </ExportOptionSelectStyled>
                                </ExportOptionHeaderStyled>
                                <ExportFieldSelectionContainerStyled>
                                    <Typography variant="subtitle2" gutterBottom>
                                        Export Field Selection
                                    </Typography>

                                    <SelectionListContainerStyled>
                                        <ColumnSelectionListStyled>
                                            <ListItem onClick={this.selectAllHandler}>
                                                Select All
                                            </ListItem>
                                            {this.state.columnsDetail.map(column => (
                                                <ListItem
                                                    key={column.columnName}
                                                    button
                                                    className={classes.listItemOverride}
                                                >
                                                    <CheckableItem
                                                        onSelectionChange={this.columnSelectionHandler(
                                                            column
                                                        )}
                                                        label={column.columnName}
                                                        selected={column.isSelected}
                                                    />
                                                </ListItem>
                                            ))}
                                        </ColumnSelectionListStyled>

                                        <RegionSelectionListStyled>
                                            {[0, 1, 2, 3].map(value => (
                                                <ListItem
                                                    key={value}
                                                    button
                                                    className={classes.listItemOverride}
                                                >
                                                    <CheckableItem
                                                        onSelectionChange={this.columnSelectionHandler(
                                                            value
                                                        )}
                                                        label={`Line item ${value + 1}`}
                                                        selected={
                                                            this.state.selectedColumns.indexOf(
                                                                value
                                                            ) !== -1
                                                        }
                                                    />
                                                </ListItem>
                                            ))}
                                        </RegionSelectionListStyled>
                                    </SelectionListContainerStyled>
                                </ExportFieldSelectionContainerStyled>
                            </MainContainerStyled>
                        </MyPaper>
                    </ThemeProvider>
                </Modal>
            </div>
        );
    }
}

ExportModal.propTypes = {
    classes: PropTypes.object.isRequired
};

// We need an intermediary variable for handling the recursive nesting.
export const ExportModalWrapped = withStyles(styles)(ExportModal);

// export default ExportModalWrapped;
