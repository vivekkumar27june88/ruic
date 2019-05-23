import Icon from '@material-ui/core/Icon';
import { withStyles } from '@material-ui/core/styles';
import React from 'react';
import styled from 'styled-components';

const MainContainer = styled.div`
    display: flex;
    flex-direction: row;
    justify-content: space-between;
    min-height: 20px;
    width: 100%;
    background-color: ${props => (props.selected ? '#ccc' : '#fff')};
    font-weight: ${props => (props.selected ? 'bold' : 'normal')};
    padding: 15px;
    transition: all 0.4s ease;
`;

const SelectIcon = styled(Icon)`
    display: ${props => (props.selected ? 'block' : 'none')};
`;

const styles = theme => ({});

export class CheckableItem extends React.Component {
    clickHandler = () => {
        this.props.onSelectionChange(!this.props.selected);
    };

    render() {
        return (
            <MainContainer selected={this.props.selected} onClick={this.clickHandler}>
                <div>{this.props.label}</div>
                <SelectIcon selected={this.props.selected}>done</SelectIcon>
            </MainContainer>
        );
    }
}

// export default CheckableItem;
export const CheckableItemWrapped = withStyles(styles)(CheckableItem);
